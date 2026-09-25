/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap
public import Mathlib.Topology.Algebra.Group.Units
/-!
# Principal-unit decomposition

This file connects the principal-unit decomposition proved in
`PrincipalUnits` to the standard integer-valued field-unit valuation attached
to a `ℤᵐ⁰`-valued complete discrete valuation.
-/

@[expose] public section

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup renaming
  roots_principalUnit_uniformizer_zpow_eq_iff →
    roots_principalUnit_uniformizer_zpow_eq_iff

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  multiplicativeIntegerValuationOfUniformizer →
    multiplicativeIntegerValuationOfUniformizer

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  multiplicativeIntegerValuationOfUniformizer_isUniformizer →
    multiplicativeIntegerValuationOfUniformizer_isUniformizer

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup →
    multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  uniformizerValueExponent →
    uniformizerValueExponent

open _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF renaming
  uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit →
    uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit


noncomputable section

open Filter
open scoped Topology
open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

namespace LocalFieldTheory.DiscreteValuationField
namespace CompleteDVF
namespace higherPrincipalUnitGroup

variable {K : Type u} [Field K]

/-- The uniformizer–residue–principal-unit decomposition, complete-DVF form: every field unit is a
product of a lifted residue root of unity, a first principal unit, and an
integral power of a chosen uniformizer. -/
theorem exists_roots_principalUnit_uniformizer_zpow_of_completeDVF
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    ∃ ζ : residueRootsOfUnityGroup F,
    ∃ p : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1,
    ∃ n : ℤ,
      x =
        valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) *
          (Units.mk0 (π : K) hπ.ne_zero) ^ n := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  simpa [V] using
    exists_roots_principalUnit_uniformizer_zpow_of_zeroSubgroup_eq_unitGroup
      (F := F) V hzero hπV x

/-- Uniqueness part of the uniformizer–residue–principal-unit decomposition for an arbitrary
complete DVF and fixed uniformizer. -/
theorem roots_principalUnit_uniformizer_zpow_eq_iff_of_completeDVF
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (ζ η : residueRootsOfUnityGroup F)
    (p q : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)
      (m n : ℤ) :
    valuationSubringUnitFieldUnitHom F
          (ζ : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (p : F.valuationSubringˣ) *
        (Units.mk0 (π : K) hπ.ne_zero) ^ m =
      valuationSubringUnitFieldUnitHom F
          (η : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (q : F.valuationSubringˣ) *
        (Units.mk0 (π : K) hπ.ne_zero) ^ n ↔
      ζ = η ∧ p = q ∧ m = n := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  simpa [V] using
    roots_principalUnit_uniformizer_zpow_eq_iff_of_zeroSubgroup_eq_unitGroup
      (F := F) V hzero hπV ζ η p q m n

/-- The uniformizer–residue–principal-unit decomposition, group-isomorphism form for a complete
DVF with a fixed uniformizer:
`K^* ≃ μ_{q-1} × U^1 × ℤ`. -/
noncomputable def fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    fieldUnitDecompositionFactors F ≃* Kˣ := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  exact
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfZeroSubgroupEqUnitGroup
      (F := F) V hzero hπV

/--
The defining evaluation formula for `fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF`
is `fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ z =
valuationSubringUnitFieldUnitHom F (z.1.1 : F.valuationSubringˣ) *
valuationSubringUnitFieldUnitHom F (z.1.2 : F.valuationSubringˣ) * (Units.mk0 (π : K) hπ.ne_zero)
^ Multiplicative.toAdd z.2`.
-/
@[simp]
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (z : fieldUnitDecompositionFactors F) :
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ z =
      valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) *
        (Units.mk0 (π : K) hπ.ne_zero) ^ Multiplicative.toAdd z.2 := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F)
        hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have happ :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizer_apply
      F V
      (fun y =>
        mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
          (F := F) V hzero y)
      hπV z
  simp [fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF,
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfZeroSubgroupEqUnitGroup]

/--
Establishes the identity `((CompleteDVF.multiplicativeIntegerValuationOfUniformizer F) hπ).val
(fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ z) = Multiplicative.toAdd z.2`.
-/
theorem multiplicativeIntegerValuationOfUniformizer_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (z : fieldUnitDecompositionFactors F) :
    ((multiplicativeIntegerValuationOfUniformizer F) hπ).val
        (fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
          F hπ z) =
      Multiplicative.toAdd z.2 := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          valuationSubringUnitFieldUnitHom F u = y := by
    intro y
    exact
      mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
        (F := F) V
        (by
          simpa [V] using
            (multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F) hπ)
        y
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have hunit :
      valuationSubringUnitFieldUnitHom F
            (z.1.1 : F.valuationSubringˣ) *
          valuationSubringUnitFieldUnitHom F
            (z.1.2 : F.valuationSubringˣ) ∈
        V.zeroSubgroup :=
    (hzero _).2
      ⟨(z.1.1 : F.valuationSubringˣ) * (z.1.2 : F.valuationSubringˣ), by
        rw [map_mul]⟩
  rw [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]
  exact V.valuation_uniformizer_normal_form hπV hunit (Multiplicative.toAdd z.2)

/--
Establishes the identity `(CompleteDVF.uniformizerValueExponent F) hπ
(fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ z) = Multiplicative.toAdd z.2`.
-/
theorem uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (z : fieldUnitDecompositionFactors F) :
    (uniformizerValueExponent F) hπ
        (fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
          F hπ z) =
      Multiplicative.toAdd z.2 :=
  multiplicativeIntegerValuationOfUniformizer_fieldUnitsEquivRootsPrincipalUnitsUniformizer
    F hπ z

/--
Establishes the identity `Multiplicative.toAdd
((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ).symm x).2 =
(CompleteDVF.uniformizerValueExponent F) hπ x`.
-/
theorem uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    Multiplicative.toAdd
        ((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
          F hπ).symm x).2 =
      (uniformizerValueExponent F) hπ
        x := by
  have h :=
    uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer
      F hπ
      ((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ).symm x)
  simpa using h.symm

/--
Establishes the identity `((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F
hπ).symm x).2 = Multiplicative.ofAdd ((CompleteDVF.uniformizerValueExponent F) hπ x)`.
-/
@[simp]
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    ((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F hπ).symm x).2 =
      Multiplicative.ofAdd
        ((uniformizerValueExponent F)
        hπ x) := by
  let E :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F hπ
  have h :
      Multiplicative.toAdd ((E.symm x).2) =
        (uniformizerValueExponent F)
          hπ x := by
    exact uniformizerValueExponent_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm F hπ x
  calc
    (E.symm x).2 = Multiplicative.ofAdd (Multiplicative.toAdd ((E.symm x).2)) := by
      simp
    _ = Multiplicative.ofAdd
      ((uniformizerValueExponent F)
      hπ x) := by
      rw [h]

/--
`fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_factors_mul_uniformizer` satisfies the
integer-power formula `valuationSubringUnitFieldUnitHom F
(((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ).symm x).1.1 :
F.valuationSubringˣ) * valuationSubringUnitFieldUnitHom F
(((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ).symm x).1.2 :
F.valuationSubringˣ) * (Units.mk0 (π : K) hπ.ne_zero) ^ (CompleteDVF.uniformizerValueExponent F)
hπ x = x`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_factors_mul_uniformizer_zpow
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
            F hπ).symm x).1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
            F hπ).symm x).1.2 : F.valuationSubringˣ) *
        (Units.mk0 (π : K) hπ.ne_zero) ^
          (uniformizerValueExponent
          F) hπ x =
      x := by
  let E :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F hπ
  have hexp :
      Multiplicative.toAdd ((E.symm x).2) =
        (uniformizerValueExponent F)
          hπ x := by
    simp [E]
  calc
    valuationSubringUnitFieldUnitHom F
          (((E.symm x).1.1 : F.valuationSubringˣ)) *
        valuationSubringUnitFieldUnitHom F
          (((E.symm x).1.2 : F.valuationSubringˣ)) *
        (Units.mk0 (π : K) hπ.ne_zero) ^
          (uniformizerValueExponent
          F) hπ x =
        valuationSubringUnitFieldUnitHom F
            (((E.symm x).1.1 : F.valuationSubringˣ)) *
          valuationSubringUnitFieldUnitHom F
            (((E.symm x).1.2 : F.valuationSubringˣ)) *
          (Units.mk0 (π : K) hπ.ne_zero) ^ Multiplicative.toAdd ((E.symm x).2) := by
          rw [hexp]
    _ = E (E.symm x) := by
          rw [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply]
    _ = x := E.apply_symm_apply x

/--
`fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitPart_eq_mul_uniformizer_zpow` satisfies
the negation formula `valuationSubringUnitFieldUnitHom F
(((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ).symm x).1.1 :
F.valuationSubringˣ) * valuationSubringUnitFieldUnitHom F
(((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ).symm x).1.2 :
F.valuationSubringˣ) = x * (Units.mk0 (π : K) hπ.ne_zero) ^
(-((CompleteDVF.uniformizerValueExponent F) hπ x))`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitPart_eq_mul_uniformizer_zpow_neg
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
            F hπ).symm x).1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
            F hπ).symm x).1.2 : F.valuationSubringˣ) =
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((uniformizerValueExponent
          F) hπ x)) := by
  let ϖ : Kˣ := Units.mk0 (π : K) hπ.ne_zero
  let u : Kˣ :=
    valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
            F hπ).symm x).1.1 : F.valuationSubringˣ) *
        valuationSubringUnitFieldUnitHom F
          (((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
            F hπ).symm x).1.2 : F.valuationSubringˣ)
  have hux :
      u * ϖ ^
        (uniformizerValueExponent F)
        hπ x = x := by
    simpa [u, ϖ] using
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_factors_mul_uniformizer_zpow
        F hπ x
  calc
    u = u * 1 := by simp
    _ = u * (ϖ ^
      (uniformizerValueExponent F) hπ x *
        ϖ ^ (-((uniformizerValueExponent F) hπ x))) := by
          rw [← zpow_add, add_neg_cancel, zpow_zero]
    _ = x * ϖ ^
      (-((uniformizerValueExponent F)
      hπ x)) := by
          rw [← mul_assoc, hux]

/--
Establishes the membership statement `x * (Units.mk0 (π : K) hπ.ne_zero) ^
(-((CompleteDVF.uniformizerValueExponent F) hπ x)) ∈ F.valuation.valuationSubring.unitGroup`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_unitPart_mem_unitGroup
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((uniformizerValueExponent
          F) hπ x)) ∈
      F.valuation.valuationSubring.unitGroup := by
  let V : MultiplicativeIntegerValuation Kˣ :=
    (multiplicativeIntegerValuationOfUniformizer F) hπ
  have hzero :
      V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_zeroSubgroup_eq_unitGroup F) hπ
  have hπV :
      V.IsUniformizer (Units.mk0 (π : K) hπ.ne_zero) := by
    simpa [V] using
      (multiplicativeIntegerValuationOfUniformizer_isUniformizer F) hπ
  have hmem :
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
          (-((uniformizerValueExponent F) hπ x)) ∈
        V.zeroSubgroup := by
    rw [V.mem_zeroSubgroup_iff, V.val_mul, V.val_uniformizer_zpow hπV]
    simp [V]
  simpa [hzero] using hmem

/-- The valuation-ring unit obtained by removing the uniformizer power from a
field unit. -/
noncomputable def fieldUnitUniformizerUnitPart
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) : F.valuationSubringˣ :=
  F.valuation.valuationSubring.unitGroupMulEquiv
    ⟨x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((uniformizerValueExponent
          F) hπ x)),
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_unitPart_mem_unitGroup
        F hπ x⟩

/--
Establishes the identity `valuationSubringUnitFieldUnitHom F (fieldUnitUniformizerUnitPart F hπ x)
= x * (Units.mk0 (π : K) hπ.ne_zero) ^ (-((CompleteDVF.uniformizerValueExponent F) hπ x))`.
-/
@[simp]
theorem valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    valuationSubringUnitFieldUnitHom F
        (fieldUnitUniformizerUnitPart F hπ x) =
      x * (Units.mk0 (π : K) hπ.ne_zero) ^
        (-((uniformizerValueExponent
          F) hπ x)) := by
  apply Units.ext
  simp [valuationSubringUnitFieldUnitHom, fieldUnitUniformizerUnitPart]

/--
Establishes the identity `(((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F
hπ).symm x).1.1 : F.valuationSubringˣ) *
(((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F hπ).symm x).1.2 :
F.valuationSubringˣ) = fieldUnitUniformizerUnitPart F hπ x`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitSubringUnit_eq
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    (((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F hπ).symm x).1.1 : F.valuationSubringˣ) *
        (((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
          F hπ).symm x).1.2 : F.valuationSubringˣ) =
      fieldUnitUniformizerUnitPart F hπ x := by
  apply valuationSubringUnitFieldUnitHom_injective
  rw [map_mul]
  rw [fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitPart_eq_mul_uniformizer_zpow_neg]
  rw [valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart]

/--
Establishes the identity `((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF F
hπ).symm x).1 = (valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm
(fieldUnitUniformizerUnitPart F hπ x)`.
-/
theorem fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_fst_eq_unitPart
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    ((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F hπ).symm x).1 =
      (valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm
        (fieldUnitUniformizerUnitPart F hπ x) := by
  apply (valuationSubringUnitsEquivRootsTimesPrincipalUnits
    F).injective
  simpa [valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply]
    using
      fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_unitSubringUnit_eq
        F hπ x

/-- Equality of range-restricted values forces equality of the integral
uniformizer exponents. -/
theorem uniformizerValueExponent_eq_of_mrangeRestrict_eq
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    {x y : Kˣ}
    (hxy :
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (y : K) =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrict F) (x : K)) :
    (uniformizerValueExponent F) hπ y =
      (uniformizerValueExponent F) hπ
        x := by
  have hval : F.valuation (y : K) = F.valuation (x : K) :=
    congrArg Subtype.val hxy
  apply
    ((_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit_zpow_inj
    F) hπ).1
  calc
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
      (uniformizerValueExponent F) hπ y =
        (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) y := by
      rw [(uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]
    _ = (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.fieldUnitValueUnit F) x := by
      ext
      simpa [CompleteDVF.fieldUnitValueUnit] using hval
    _ = (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueUnit F) hπ ^
      (uniformizerValueExponent F) hπ
      x := by
      rw [(uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit F)]

/-- The uniformizer exponent is locally constant for the range-restricted
valuation topology. -/
theorem eventually_uniformizerValueExponent_eq_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K))
    (x : Kˣ) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    ∀ᶠ y : Kˣ in 𝓝 x,
      (uniformizerValueExponent F) hπ y =
        (uniformizerValueExponent F)
          hπ x := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have hxne : ((Valued.v : _root_.Valuation K Γ) (x : K) : Γ) ≠ 0 :=
    ((_root_.Valuation.ne_zero_iff
      (Valued.v : _root_.Valuation K Γ)).2 x.ne_zero)
  have hlocK :
      { y : K |
          (Valued.v : _root_.Valuation K Γ) y =
            (Valued.v : _root_.Valuation K Γ) (x : K) } ∈ 𝓝 (x : K) :=
    by
      have hxrestrictne :
          (Valued.v : _root_.Valuation K Γ).restrict (x : K) ≠ 0 :=
        ne_of_gt
          ((_root_.Valuation.restrict_pos_iff
            (Valued.v : _root_.Valuation K Γ) (x : K)).2
              (zero_lt_iff.mpr hxne))
      simpa only [_root_.Valuation.restrict_inj] using
        (Valued.isOpen_sphere K hxrestrictne).mem_nhds (by rfl)
  have hlocUnits :
      { y : Kˣ |
          (Valued.v : _root_.Valuation K Γ) (y : K) =
            (Valued.v : _root_.Valuation K Γ) (x : K) } ∈ 𝓝 x := by
    simpa [Set.preimage] using Units.continuous_val.continuousAt hlocK
  exact Filter.mem_of_superset hlocUnits fun y hy =>
    uniformizerValueExponent_eq_of_mrangeRestrict_eq
      F hπ (by
        apply Subtype.ext
        change F.valuation (y : K) = F.valuation (x : K)
        have hval := congrArg Subtype.val hy
        change F.valuation (y : K) = F.valuation (x : K) at hval
        exact hval)

/-- The integer-valued uniformizer exponent is continuous for the
range-restricted valuation topology. -/
theorem continuous_uniformizerValueExponent_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun x : Kˣ =>
      (uniformizerValueExponent F) hπ
      x) := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  rw [continuous_iff_continuousAt]
  intro x
  rw [continuousAt_def]
  intro s hs
  have hxmem :
    (uniformizerValueExponent F) hπ x
    ∈ s :=
    mem_of_mem_nhds hs
  exact
    Filter.mem_of_superset
      (eventually_uniformizerValueExponent_eq_mrangeRestrict
        F hπ x)
      (fun y hy => by
        change
          (uniformizerValueExponent
          F) hπ y ∈ s
        rw [hy]
        exact hxmem)

/-- The integer factor of the inverse decomposition map is continuous. -/
theorem continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun x : Kˣ =>
      ((fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ).symm x).2) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have hval :
      Continuous (fun x : Kˣ =>
        (uniformizerValueExponent F)
        hπ x) :=
    continuous_uniformizerValueExponent_mrangeRestrict
      F hπ
  have hofAdd :
      Continuous (fun n : ℤ => (Multiplicative.ofAdd n : Multiplicative ℤ)) :=
    continuous_of_discreteTopology
  exact (hofAdd.comp hval).congr fun x =>
    (fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd
      F hπ x).symm

/-- Removing the uniformizer power from a field unit is continuous as a map
to valuation-ring units. -/
theorem continuous_fieldUnitUniformizerUnitPart_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun x : Kˣ =>
      fieldUnitUniformizerUnitPart F hπ x) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let ϖ : Kˣ := Units.mk0 (π : K) hπ.ne_zero
  have hval :
      Continuous (fun x : Kˣ =>
        (uniformizerValueExponent F)
        hπ x) :=
    continuous_uniformizerValueExponent_mrangeRestrict
      F hπ
  have hpow :
      Continuous (fun n : ℤ => ϖ ^ (-n)) :=
    continuous_of_discreteTopology
  have hfield :
      Continuous (fun x : Kˣ =>
        x * ϖ ^
          (-((uniformizerValueExponent F) hπ x))) :=
    continuous_id.mul (hpow.comp hval)
  rw [Units.continuous_iff]
  constructor
  · have hfieldK :
        Continuous (fun x : Kˣ =>
          ((x * ϖ ^
            (-((uniformizerValueExponent F) hπ x)) : Kˣ) : K)) :=
      Units.continuous_val.comp hfield
    have hcoerced :
        Continuous (fun x : Kˣ =>
          ((fieldUnitUniformizerUnitPart F hπ x :
              F.valuationSubring) : K)) := by
      convert hfieldK using 1
      funext x
      calc
        _ = ((valuationSubringUnitFieldUnitHom F
              (fieldUnitUniformizerUnitPart F hπ x) : Kˣ) : K) :=
          (coe_valuationSubringUnitFieldUnitHom_apply F
            (fieldUnitUniformizerUnitPart F hπ x)).symm
        _ = _ :=
          congrArg (fun y : Kˣ => (y : K))
            (valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
              F hπ x)
    exact Continuous.subtype_mk hcoerced fun x =>
      (fieldUnitUniformizerUnitPart F hπ x :
        F.valuationSubring).2
  · have hfieldInvK :
        Continuous (fun x : Kˣ =>
          (((x * ϖ ^
            (-((uniformizerValueExponent F) hπ x)) : Kˣ)⁻¹ :
              Kˣ) : K)) :=
      Units.continuous_val.comp hfield.inv
    have hcoercedInv :
        Continuous (fun x : Kˣ =>
          ((((fieldUnitUniformizerUnitPart F hπ x)⁻¹ :
              F.valuationSubringˣ) : F.valuationSubring) : K)) := by
      convert hfieldInvK using 1
      funext x
      calc
        _ = ((valuationSubringUnitFieldUnitHom F
              ((fieldUnitUniformizerUnitPart F hπ x)⁻¹) : Kˣ) : K) :=
          (coe_valuationSubringUnitFieldUnitHom_apply F
            ((fieldUnitUniformizerUnitPart F hπ x)⁻¹)).symm
        _ = (((valuationSubringUnitFieldUnitHom F
              (fieldUnitUniformizerUnitPart F hπ x))⁻¹ : Kˣ) : K) := by
          rw [map_inv]
        _ = _ :=
          congrArg (fun y : Kˣ => ((y⁻¹ : Kˣ) : K))
            (valuationSubringUnitFieldUnitHom_fieldUnitUniformizerUnitPart
              F hπ x)
    exact Continuous.subtype_mk hcoercedInv fun x =>
      (((fieldUnitUniformizerUnitPart F hπ x)⁻¹ :
          F.valuationSubringˣ) : F.valuationSubring).2

/-- The first principal-unit subgroup is open in valuation-ring units for the
range-restricted valuation topology. -/
theorem isOpen_higherPrincipalUnitGroup_one_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    IsOpen (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1
      : Set F.valuationSubringˣ)) := by
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  let : Valued K Γ :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  rw [isOpen_iff_mem_nhds]
  intro u hu
  have hu_lt :
      F.valuation (((u : F.valuationSubring) - 1 : F.valuationSubring) : K) < 1 := by
    have hu_mem :
        ((u : F.valuationSubring) - 1 : F.valuationSubring) ∈ F.maximalIdeal := by
      simpa [mem_iff] using hu
    simpa using
      (_root_.Valuation.mem_maximalIdeal_iff K F.valuation).1 hu_mem
  have htoK :
      Continuous (fun y : F.valuationSubringˣ =>
        ((y : F.valuationSubring) : K)) :=
    continuous_subtype_val.comp Units.continuous_val
  have hballK :
      { y : K |
          (Valued.v : _root_.Valuation K Γ)
            (y - ((u : F.valuationSubring) : K)) < (1 : Γ) } ∈
        𝓝 (((u : F.valuationSubring) : K)) := by
    rw [Valued.mem_nhds]
    refine ⟨1, ?_⟩
    intro y hy
    have hy' :
      (Valued.v : _root_.Valuation K Γ).restrict
          (y - ((u : F.valuationSubring) : K)) < 1 := by
      simpa only [Set.mem_ofPred_eq, Units.val_one] using hy
    have hval :
      (Valued.v : _root_.Valuation K Γ)
          (y - ((u : F.valuationSubring) : K)) < 1 :=
      (_root_.Valuation.restrict_lt_one_iff
        (Valued.v : _root_.Valuation K Γ)).1 hy'
    simpa only [Set.mem_ofPred_eq] using hval
  have hballUnits :
      { y : F.valuationSubringˣ |
          (Valued.v : _root_.Valuation K Γ)
            (((y : F.valuationSubring) : K) -
              ((u : F.valuationSubring) : K)) < (1 : Γ) } ∈
        𝓝 u := by
    simpa [Set.preimage] using htoK.continuousAt hballK
  exact Filter.mem_of_superset hballUnits fun y hy => by
    have hy_lt :
        F.valuation
            (((y : F.valuationSubring) : K) -
              ((u : F.valuationSubring) : K)) < 1 := by
      exact hy
    have hdecomp :
        (((y : F.valuationSubring) - 1 : F.valuationSubring) : K) =
          (((y : F.valuationSubring) : K) -
              ((u : F.valuationSubring) : K)) +
            (((u : F.valuationSubring) - 1 : F.valuationSubring) : K) := by
      change ((y : F.valuationSubring) : K) - 1 =
        (((y : F.valuationSubring) : K) - ((u : F.valuationSubring) : K)) +
          (((u : F.valuationSubring) : K) - 1)
      ring
    have hyu_lt :
        F.valuation (((y : F.valuationSubring) - 1 : F.valuationSubring) : K) < 1 := by
      rw [hdecomp]
      exact (F.valuation.map_add _ _).trans_lt (max_lt hy_lt hu_lt)
    have hy_mem :
        ((y : F.valuationSubring) - 1 : F.valuationSubring) ∈ F.maximalIdeal :=
      (_root_.Valuation.mem_maximalIdeal_iff K F.valuation).2 hyu_lt
    simpa [mem_iff] using hy_mem

/-- The residue-unit map is locally constant on valuation-ring units. -/
theorem eventually_residueUnitHom_eq_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    (u : F.valuationSubringˣ) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    ∀ᶠ y : F.valuationSubringˣ in 𝓝 u,
      residueUnitHom F y =
        residueUnitHom F u := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let Γ : Type v :=
    MonoidHom.mrange F.valuation.toMonoidWithZeroHom
  have htoK :
      Continuous (fun y : F.valuationSubringˣ =>
        ((y : F.valuationSubring) : K)) :=
    continuous_subtype_val.comp Units.continuous_val
  have hballK :
      { y : K |
          (Valued.v : _root_.Valuation K Γ)
            (y - ((u : F.valuationSubring) : K)) < (1 : Γ) } ∈
        𝓝 (((u : F.valuationSubring) : K)) := by
    rw [Valued.mem_nhds]
    refine ⟨1, ?_⟩
    intro y hy
    simpa using hy
  have hballUnits :
      { y : F.valuationSubringˣ |
          (Valued.v : _root_.Valuation K Γ)
            (((y : F.valuationSubring) : K) -
              ((u : F.valuationSubring) : K)) < (1 : Γ) } ∈
        𝓝 u := by
    simpa [Set.preimage] using htoK.continuousAt hballK
  exact Filter.mem_of_superset hballUnits fun y hy => by
    have hy_lt :
        F.valuation
            (((y : F.valuationSubring) : K) -
              ((u : F.valuationSubring) : K)) < 1 := by
      exact hy
    have hdiff_mem :
        ((y : F.valuationSubring) - (u : F.valuationSubring) :
          F.valuationSubring) ∈ F.maximalIdeal :=
      (_root_.Valuation.mem_maximalIdeal_iff K F.valuation).2 (by
        simpa using hy_lt)
    have hres :
        F.residueMap (y : F.valuationSubring) =
          F.residueMap (u : F.valuationSubring) :=
      (ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := F.valuationSubring) (y : F.valuationSubring)
        (u : F.valuationSubring)).2 hdiff_mem
    exact
      (residueUnitHom_eq_iff_residue_eq F y u).2 hres

/--
Establishes the identity `((valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm u).1 =
(residueRootsOfUnityEquivResidueFieldUnits F).symm (residueUnitHom F u)`.
-/
theorem valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_residue
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    (u : F.valuationSubringˣ) :
    ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm u).1 =
      (residueRootsOfUnityEquivResidueFieldUnits F).symm
        (residueUnitHom F u) := by
  let E :=
    valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let R :=
    residueRootsOfUnityEquivResidueFieldUnits F
  apply R.injective
  have hp :
      residueUnitHom F
          (((E.symm u).2 : F.valuationSubringˣ)) = 1 :=
    (residueUnitHom_eq_one_iff
      F ((E.symm u).2 : F.valuationSubringˣ)).2 (E.symm u).2.property
  have hprod :
      ((E.symm u).1 : F.valuationSubringˣ) *
          ((E.symm u).2 : F.valuationSubringˣ) =
        u := by
    change E (E.symm u) = u
    exact E.apply_symm_apply u
  have hres := congrArg (residueUnitHom F) hprod
  rw [R.apply_symm_apply]
  change
    residueUnitHom F
        (((E.symm u).1 : F.valuationSubringˣ)) =
      residueUnitHom F u
  simpa [
    valuationSubringUnitsEquivRootsTimesPrincipalUnits_apply,
    map_mul, hp] using hres

/--
Establishes the identity `(((valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm u).2 :
F.valuationSubringˣ) = (((valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm u).1 :
F.valuationSubringˣ)⁻¹ * u`.
-/
theorem valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_eq
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    (u : F.valuationSubringˣ) :
    (((valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F).symm u).2 : F.valuationSubringˣ) =
      (((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).1 : F.valuationSubringˣ)⁻¹ * u := by
  let E :=
    valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  have hprod :
      ((E.symm u).1 : F.valuationSubringˣ) *
          ((E.symm u).2 : F.valuationSubringˣ) =
        u := by
    change E (E.symm u) = u
    exact E.apply_symm_apply u
  calc
    ((E.symm u).2 : F.valuationSubringˣ) =
        ((E.symm u).1 : F.valuationSubringˣ)⁻¹ *
          (((E.symm u).1 : F.valuationSubringˣ) *
            ((E.symm u).2 : F.valuationSubringˣ)) := by
      simp
    _ = ((E.symm u).1 : F.valuationSubringˣ)⁻¹ * u := by
      rw [hprod]

/-- The root-of-unity factor of the inverse unit decomposition is locally
constant. -/
theorem eventually_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    (u : F.valuationSubringˣ) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    ∀ᶠ y : F.valuationSubringˣ in 𝓝 u,
      ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm y).1 =
        ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
          F).symm u).1 := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  exact
    (eventually_residueUnitHom_eq_mrangeRestrict
      F u).mono fun y hy => by
      rw [
        valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_residue
          F y,
        valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_residue
          F u,
        hy]

/-- The root-of-unity factor of the inverse unit decomposition is continuous. -/
theorem continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).1) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  rw [continuous_iff_continuousAt]
  intro u
  rw [continuousAt_def]
  intro s hs
  have humem :
      ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).1 ∈ s :=
    mem_of_mem_nhds hs
  exact
    Filter.mem_of_superset
      (eventually_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_eq_mrangeRestrict
        F u)
      (fun y hy => by
        change
          ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
            F).symm y).1 ∈ s
        rw [hy]
        exact humem)

/-- The inclusion of valuation-ring units into field units is continuous for
the range-restricted valuation topology. -/
theorem continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      valuationSubringUnitFieldUnitHom F u) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have hsub : Continuous (fun x : F.valuationSubring => (x : K)) :=
    continuous_subtype_val
  rw [Units.continuous_iff]
  constructor
  · convert hsub.comp Units.continuous_val using 1
    funext u
    exact
      (coe_valuationSubringUnitFieldUnitHom_apply F u).symm
  · convert hsub.comp Units.continuous_coe_inv using 1
    funext u
    change
      (((valuationSubringUnitFieldUnitHom F u)⁻¹ : Kˣ) : K) =
        (((u⁻¹ : F.valuationSubringˣ) : F.valuationSubring) : K)
    rw [← map_inv]
    exact coe_valuationSubringUnitFieldUnitHom_apply F (u⁻¹)

/-- The principal-unit factor of the inverse unit decomposition is continuous
as a valuation-ring unit. -/
theorem continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_coe_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      (((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).2 : F.valuationSubringˣ)) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let E :=
    valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  let rootToField : F.valuationSubringˣ → Kˣ := fun u =>
    valuationSubringUnitFieldUnitHom F
      (((E.symm u).1 : F.valuationSubringˣ))
  let unitToField : F.valuationSubringˣ → Kˣ := fun u =>
    valuationSubringUnitFieldUnitHom F u
  have hroot :
      Continuous (fun u : F.valuationSubringˣ => (E.symm u).1) :=
    continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_mrangeRestrict
      F
  have hrootUnit :
      Continuous (fun u : F.valuationSubringˣ =>
        (((E.symm u).1 : F.valuationSubringˣ))) :=
    continuous_subtype_val.comp hroot
  have hrootField : Continuous rootToField :=
    (continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
      F).comp hrootUnit
  have hunitField : Continuous unitToField :=
    continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
      F
  have hpartField :
      Continuous (fun u : F.valuationSubringˣ =>
        (rootToField u)⁻¹ * unitToField u) :=
    hrootField.inv.mul hunitField
  rw [Units.continuous_iff]
  constructor
  · have hpartK :
        Continuous (fun u : F.valuationSubringˣ =>
          (((rootToField u)⁻¹ * unitToField u : Kˣ) : K)) :=
      Units.continuous_val.comp hpartField
    have hcoerced :
        Continuous (fun u : F.valuationSubringˣ =>
          ((((E.symm u).2 : F.valuationSubringˣ) :
            F.valuationSubring) : K)) := by
      convert hpartK using 1
      ext u
      have hsnd :=
        valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_eq
          F u
      have hfield :=
        congrArg
          (fun a : F.valuationSubringˣ =>
            ((valuationSubringUnitFieldUnitHom F a : Kˣ) : K))
          hsnd
      simpa [rootToField, unitToField, map_mul] using hfield
    exact Continuous.subtype_mk hcoerced fun u =>
      (((E.symm u).2 : F.valuationSubringˣ) : F.valuationSubring).2
  · have hpartInvK :
        Continuous (fun u : F.valuationSubringˣ =>
          ((((rootToField u)⁻¹ * unitToField u : Kˣ)⁻¹ : Kˣ) : K)) :=
      Units.continuous_val.comp hpartField.inv
    have hcoercedInv :
        Continuous (fun u : F.valuationSubringˣ =>
          (((((E.symm u).2 : F.valuationSubringˣ)⁻¹ :
            F.valuationSubringˣ) : F.valuationSubring) : K)) := by
      convert hpartInvK using 1
      ext u
      have hsnd :=
        valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_eq
          F u
      have hsndInv :
          (((E.symm u).2 : F.valuationSubringˣ)⁻¹ : F.valuationSubringˣ) =
            ((((E.symm u).1 : F.valuationSubringˣ)⁻¹ * u)⁻¹ :
              F.valuationSubringˣ) := by
        rw [hsnd]
      have hfieldInv :=
        congrArg
          (fun a : F.valuationSubringˣ =>
            ((valuationSubringUnitFieldUnitHom F a : Kˣ) : K))
          hsndInv
      change
        (((valuationSubringUnitFieldUnitHom F
          (((E.symm u).2 : F.valuationSubringˣ)))⁻¹ : Kˣ) : K) =
          ((((rootToField u)⁻¹ * unitToField u : Kˣ)⁻¹ : Kˣ) : K)
      simpa [E, rootToField, unitToField, map_mul] using hfieldInv
    exact Continuous.subtype_mk hcoercedInv fun u =>
      ((((E.symm u).2 : F.valuationSubringˣ)⁻¹ :
        F.valuationSubringˣ) : F.valuationSubring).2

/-- The principal-unit factor of the inverse unit decomposition is continuous. -/
theorem continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u).2) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let E :=
    valuationSubringUnitsEquivRootsTimesPrincipalUnits
      F
  exact
    Continuous.subtype_mk
      (continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_coe_mrangeRestrict
        F)
      (fun u => (E.symm u).2.property)

/-- The inverse of the unit-level decomposition `Oˣ ≃ μ × U¹` is continuous. -/
theorem continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField] :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun u : F.valuationSubringˣ =>
      (valuationSubringUnitsEquivRootsTimesPrincipalUnits
        F).symm u) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  have hfst :
      Continuous (fun u : F.valuationSubringˣ =>
        ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
          F).symm u).1) :=
    continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_fst_mrangeRestrict
      F
  have hsnd :
      Continuous (fun u : F.valuationSubringˣ =>
        ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
          F).symm u).2) :=
    continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_snd_mrangeRestrict
      F
  rw [continuous_iff_continuousAt]
  intro u
  rw [ContinuousAt, nhds_prod_eq]
  intro s hs
  rcases Filter.mem_prod_iff.1 hs with ⟨s₁, hs₁, s₂, hs₂, hsubset⟩
  have hpre₁ :
      {x : F.valuationSubringˣ |
        ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
          F).symm x).1 ∈ s₁} ∈ 𝓝 u :=
    hfst.tendsto u hs₁
  have hpre₂ :
      {x : F.valuationSubringˣ |
        ((valuationSubringUnitsEquivRootsTimesPrincipalUnits
          F).symm x).2 ∈ s₂} ∈ 𝓝 u :=
    hsnd.tendsto u hs₂
  exact Filter.mem_of_superset (Filter.inter_mem hpre₁ hpre₂) fun x hx =>
    hsubset ⟨hx.1, hx.2⟩

/-- Topological half of the uniformizer–residue–principal-unit decomposition: for the
range-restricted valuation topology, the product map
`μ × U¹ × ℤ → Kˣ` is continuous.  The inverse-continuity packaging is kept
separate from the algebraic decomposition. -/
theorem continuous_rootsPrincipalUnitUniformizerMulHom_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun z : fieldUnitDecompositionFactors F =>
      rootsPrincipalUnitUniformizerMulHom F
        (Units.mk0 (π : K) hπ.ne_zero) z) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  dsimp [rootsPrincipalUnitUniformizerMulHom]
  have hζ :
      Continuous fun z : fieldUnitDecompositionFactors F =>
        valuationSubringUnitFieldUnitHom F
          (z.1.1 : F.valuationSubringˣ) := by
    exact
      (continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
        F).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  have hp :
      Continuous fun z : fieldUnitDecompositionFactors F =>
        valuationSubringUnitFieldUnitHom F
          (z.1.2 : F.valuationSubringˣ) := by
    exact
      (continuous_valuationSubringUnitFieldUnitHom_mrangeRestrict
        F).comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  have hn :
      Continuous fun z : fieldUnitDecompositionFactors F =>
        (Units.mk0 (π : K) hπ.ne_zero : Kˣ) ^ Multiplicative.toAdd z.2 := by
    exact continuous_of_discreteTopology.comp continuous_snd
  exact (hζ.mul hp).mul hn

/-- public continuity statement for the forward map in the
`K^* ≃ μ_{q-1} × U^1 × ℤ` decomposition. -/
theorem continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun z : fieldUnitDecompositionFactors F =>
      fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ z) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  simpa only
      [fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_apply,
        rootsPrincipalUnitUniformizerMulHom_apply]
    using
      continuous_rootsPrincipalUnitUniformizerMulHom_mrangeRestrict
        F hπ

/-- The inverse map in the `K^* ≃ μ × U^1 × ℤ` decomposition is continuous. -/
theorem continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_mrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    Continuous (fun x : Kˣ =>
      (fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ).symm x) := by
  let : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  let E :=
    fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
      F hπ
  have hfstComp :
      Continuous (fun x : Kˣ =>
        (valuationSubringUnitsEquivRootsTimesPrincipalUnits
          F).symm
          (fieldUnitUniformizerUnitPart F hπ x)) :=
    (continuous_valuationSubringUnitsEquivRootsTimesPrincipalUnits_symm_mrangeRestrict
      F).comp
      (continuous_fieldUnitUniformizerUnitPart_mrangeRestrict
        F hπ)
  have hfst :
      Continuous (fun x : Kˣ => (E.symm x).1) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt]
    have hpoint (y : Kˣ) :
        (E.symm y).1 =
          (valuationSubringUnitsEquivRootsTimesPrincipalUnits F).symm
            (fieldUnitUniformizerUnitPart F hπ y) := by
      dsimp only [E]
      exact
        fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_fst_eq_unitPart
          F hπ y
    rw [hpoint x]
    exact Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun y => (hpoint y).symm)
      (hfstComp.tendsto x)
  have hsnd :
      Continuous (fun x : Kˣ => (E.symm x).2) := by
    simpa [E] using
      continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_snd_mrangeRestrict
        F hπ
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, nhds_prod_eq]
  intro s hs
  rcases Filter.mem_prod_iff.1 hs with ⟨s₁, hs₁, s₂, hs₂, hsubset⟩
  have hpre₁ : {y : Kˣ | (E.symm y).1 ∈ s₁} ∈ 𝓝 x :=
    hfst.tendsto x hs₁
  have hpre₂ : {y : Kˣ | (E.symm y).2 ∈ s₂} ∈ 𝓝 x :=
    hsnd.tendsto x hs₂
  exact Filter.mem_of_superset (Filter.inter_mem hpre₁ hpre₂) fun y hy =>
    hsubset ⟨hy.1, hy.2⟩

/-- The uniformizer–residue–principal-unit decomposition, topological group-isomorphism form for
the range-restricted valuation topology. -/
noncomputable def
  fieldUnitsContinuousMulEquivRootsPrincipalUnitsUniformizerOfCompleteDVFMrangeRestrict
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) [Finite F.residueField]
    {π : F.valuationSubring} (hπ : F.valuation.IsUniformizer (π : K)) :
    letI : Valued K
        (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
      (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
    fieldUnitDecompositionFactors F ≃ₜ* Kˣ := by
  letI : Valued K
      (MonoidHom.mrange F.valuation.toMonoidWithZeroHom) :=
    (_root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.mrangeRestrictValued F)
  exact
    { fieldUnitsEquivRootsPrincipalUnitsUniformizerOfCompleteDVF
        F hπ with
      continuous_toFun :=
        continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_of_completeDVF_mrangeRestrict
          F hπ
      continuous_invFun :=
        continuous_fieldUnitsEquivRootsPrincipalUnitsUniformizer_symm_mrangeRestrict
          F hπ }

/-- The uniformizer–residue–principal-unit decomposition, standard `ℤᵐ⁰`-valued form:
every field unit is a product of a lifted residue root of unity, a first
principal unit, and an integral power of a uniformizer. -/
theorem exists_roots_principalUnit_uniformizer_zpow_of_withZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    {ϖ : Kˣ} (hϖ : v (ϖ : K) = WithZero.exp (-1 : ℤ)) (x : Kˣ) :
    let F : CompleteDVF K :=
      { ValueGroup := WithZero (Multiplicative ℤ)
        valuation := v
        instCompleteDiscrete := inferInstance }
    letI : Finite F.residueField := by
      change Finite (IsLocalRing.ResidueField v.valuationSubring)
      infer_instance
    ∃ ζ : residueRootsOfUnityGroup F,
    ∃ p : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1,
    ∃ n : ℤ,
      x =
        valuationSubringUnitFieldUnitHom F
            (ζ : F.valuationSubringˣ) *
          valuationSubringUnitFieldUnitHom F
            (p : F.valuationSubringˣ) *
          ϖ ^ n := by
  let F : CompleteDVF K :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := v
      instCompleteDiscrete := inferInstance }
  let V : MultiplicativeIntegerValuation Kˣ :=
    MultiplicativeIntegerValuation.ofWithZeroValuation v
  have : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  have hzero : V.zeroSubgroup = F.valuation.valuationSubring.unitGroup := by
    simpa [F, V] using
      MultiplicativeIntegerValuation.ofWithZeroValuation_zeroSubgroup_eq_unitGroup
        (K := K) v
  have hϖV : V.IsUniformizer ϖ := by
    simpa [V] using
      MultiplicativeIntegerValuation.ofWithZeroValuation_isUniformizer_of_valuation_eq_exp_neg
        (K := K) v ϖ hϖ
  simpa [F, V] using
    exists_roots_principalUnit_uniformizer_zpow_of_zeroSubgroup_eq_unitGroup
      (F := F) V hzero hϖV x

/-- Uniqueness part of the uniformizer–residue–principal-unit decomposition in the same standard
`ℤᵐ⁰`-valued form. -/
theorem roots_principalUnit_uniformizer_zpow_eq_iff_of_withZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    {ϖ : Kˣ} (hϖ : v (ϖ : K) = WithZero.exp (-1 : ℤ)) :
    let F : CompleteDVF K :=
      { ValueGroup := WithZero (Multiplicative ℤ)
        valuation := v
        instCompleteDiscrete := inferInstance }
    letI : Finite F.residueField := by
      change Finite (IsLocalRing.ResidueField v.valuationSubring)
      infer_instance
    ∀ (ζ η : residueRootsOfUnityGroup F)
      (p q : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)
        (m n : ℤ),
        valuationSubringUnitFieldUnitHom F
              (ζ : F.valuationSubringˣ) *
            valuationSubringUnitFieldUnitHom F
              (p : F.valuationSubringˣ) *
            ϖ ^ m =
          valuationSubringUnitFieldUnitHom F
              (η : F.valuationSubringˣ) *
            valuationSubringUnitFieldUnitHom F
              (q : F.valuationSubringˣ) *
            ϖ ^ n ↔
          ζ = η ∧ p = q ∧ m = n := by
  let F : CompleteDVF K :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := v
      instCompleteDiscrete := inferInstance }
  let V : MultiplicativeIntegerValuation Kˣ :=
    MultiplicativeIntegerValuation.ofWithZeroValuation v
  have : Finite F.residueField := by
    change Finite (IsLocalRing.ResidueField v.valuationSubring)
    infer_instance
  have hzero :
      ∀ y : Kˣ, y ∈ V.zeroSubgroup ↔
        ∃ u : F.valuationSubringˣ,
          valuationSubringUnitFieldUnitHom F u = y := by
    intro y
    exact
      mem_zeroSubgroup_iff_exists_valuationSubringUnitFieldUnitHom_eq
        (F := F) V
        (by
          simpa [F, V] using
            MultiplicativeIntegerValuation.ofWithZeroValuation_zeroSubgroup_eq_unitGroup
              (K := K) v)
        y
  have hϖV : V.IsUniformizer ϖ := by
    simpa [V] using
      MultiplicativeIntegerValuation.ofWithZeroValuation_isUniformizer_of_valuation_eq_exp_neg
        (K := K) v ϖ hϖ
  dsimp
  intro ζ η p q m n
  simpa [F, V] using
    roots_principalUnit_uniformizer_zpow_eq_iff
      F V hzero hϖV ζ η p q m n

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
